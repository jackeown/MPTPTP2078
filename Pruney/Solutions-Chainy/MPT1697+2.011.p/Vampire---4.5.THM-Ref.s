%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:27 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  220 (2598 expanded)
%              Number of leaves         :   28 (1232 expanded)
%              Depth                    :   30
%              Number of atoms          : 1310 (38077 expanded)
%              Number of equality atoms :  229 (8451 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f678,f1227,f1241,f1256])).

fof(f1256,plain,
    ( spl6_3
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1255])).

fof(f1255,plain,
    ( $false
    | spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1254,f650])).

fof(f650,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(resolution,[],[f230,f259])).

fof(f259,plain,(
    r1_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f78,f250])).

fof(f250,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f247,f131])).

fof(f131,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f127,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f92,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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

fof(f127,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f126,f61])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f49,f48,f47,f46,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f126,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f125,f63])).

fof(f63,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f125,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f65,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f65,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f247,plain,(
    k1_setfam_1(k2_tarski(sK2,sK3)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f103,f132])).

fof(f132,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f127,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f103,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f80,f79])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f230,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | k1_xboole_0 = k7_relat_1(sK4,X1) ) ),
    inference(subsumption_resolution,[],[f228,f151])).

fof(f151,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f68,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f228,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | k1_xboole_0 = k7_relat_1(sK4,X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f76,f216])).

fof(f216,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f215,f151])).

fof(f215,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f214,f150])).

fof(f150,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f68,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f214,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f170,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f170,plain,(
    v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f169,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f169,plain,
    ( v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f168,f66])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f168,plain,
    ( ~ v1_funct_1(sK4)
    | v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f152,f67])).

fof(f67,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f152,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f68,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f1254,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_3
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1253,f674])).

fof(f674,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(resolution,[],[f236,f369])).

fof(f369,plain,(
    r1_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f78,f256])).

fof(f256,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f253,f140])).

fof(f140,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK3,sK2)) ),
    inference(resolution,[],[f134,f105])).

fof(f134,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f127,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f253,plain,(
    k1_setfam_1(k2_tarski(sK3,sK2)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f103,f141])).

fof(f141,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f134,f90])).

fof(f236,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X1) ) ),
    inference(subsumption_resolution,[],[f234,f184])).

fof(f184,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f71,f97])).

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f234,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X1)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f76,f222])).

fof(f222,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f221,f184])).

fof(f221,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f220,f183])).

fof(f183,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(resolution,[],[f71,f98])).

fof(f220,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f202,f88])).

fof(f202,plain,(
    v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f201,f60])).

fof(f201,plain,
    ( v1_partfun1(sK5,sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f200,f69])).

fof(f69,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f200,plain,
    ( ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f185,f70])).

fof(f70,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f185,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,sK3)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f71,f82])).

fof(f1253,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1252,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f1252,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1251,f64])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f1251,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1250,f123])).

fof(f123,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1250,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1248,f1225])).

fof(f1225,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f1224,plain,
    ( spl6_28
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1248,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f847,f463])).

fof(f463,plain,(
    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3) ),
    inference(superposition,[],[f131,f136])).

fof(f136,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(resolution,[],[f64,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f96,f79])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f847,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f846,f61])).

fof(f846,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f845,f66])).

fof(f845,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f844,f67])).

fof(f844,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3)
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f832,f68])).

fof(f832,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(superposition,[],[f349,f166])).

fof(f166,plain,(
    ! [X6] : k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6) ),
    inference(subsumption_resolution,[],[f149,f66])).

fof(f149,plain,(
    ! [X6] :
      ( k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f68,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f349,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10) ) ),
    inference(subsumption_resolution,[],[f348,f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1)
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f192,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f191,f60])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f190,f63])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f189,f69])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1)
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
    inference(subsumption_resolution,[],[f180,f70])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1)
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
    inference(resolution,[],[f71,f101])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f348,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10) ) ),
    inference(subsumption_resolution,[],[f347,f198])).

fof(f198,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f197,f77])).

fof(f197,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f196,f60])).

fof(f196,plain,(
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
    inference(subsumption_resolution,[],[f195,f63])).

fof(f195,plain,(
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
    inference(subsumption_resolution,[],[f194,f69])).

fof(f194,plain,(
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
    inference(subsumption_resolution,[],[f181,f70])).

fof(f181,plain,(
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
    inference(resolution,[],[f71,f102])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f347,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10) ) ),
    inference(subsumption_resolution,[],[f346,f77])).

fof(f346,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10)
      | v1_xboole_0(X9) ) ),
    inference(subsumption_resolution,[],[f345,f60])).

fof(f345,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X9) ) ),
    inference(subsumption_resolution,[],[f344,f63])).

fof(f344,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X9) ) ),
    inference(subsumption_resolution,[],[f343,f69])).

fof(f343,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X9) ) ),
    inference(subsumption_resolution,[],[f342,f70])).

fof(f342,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ v1_funct_2(sK5,sK3,sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X9) ) ),
    inference(subsumption_resolution,[],[f321,f71])).

fof(f321,plain,(
    ! [X10,X11,X9] :
      ( k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3))
      | ~ m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5))
      | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(sK5,sK3,sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
      | ~ v1_funct_2(X11,X10,sK1)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X9))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X9) ) ),
    inference(superposition,[],[f109,f199])).

fof(f199,plain,(
    ! [X6] : k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6) ),
    inference(subsumption_resolution,[],[f182,f69])).

fof(f182,plain,(
    ! [X6] :
      ( k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f71,f99])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f1241,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1240])).

fof(f1240,plain,
    ( $false
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1239,f59])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1239,plain,
    ( v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1238,f60])).

fof(f1238,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1237,f61])).

fof(f1237,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1236,f62])).

fof(f1236,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1235,f63])).

fof(f1235,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1234,f64])).

fof(f1234,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1233,f66])).

fof(f1233,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1232,f67])).

fof(f1232,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1231,f68])).

fof(f1231,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1230,f69])).

fof(f1230,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1229,f70])).

fof(f1229,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
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
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1228,f71])).

fof(f1228,plain,
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
    | spl6_28 ),
    inference(resolution,[],[f1226,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(cnf_transformation,[],[f43])).

fof(f1226,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f1227,plain,
    ( spl6_2
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1222,f1224,f117])).

fof(f117,plain,
    ( spl6_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1222,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f1221,f650])).

fof(f1221,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f1220,f674])).

fof(f1220,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f1219,f62])).

fof(f1219,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f1198,f64])).

fof(f1198,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f823,f463])).

fof(f823,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f822,f61])).

fof(f822,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f821,f66])).

fof(f821,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f820,f67])).

fof(f820,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2)
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f808,f68])).

fof(f808,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
      | ~ v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2) ) ),
    inference(superposition,[],[f341,f166])).

fof(f341,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f340,f193])).

fof(f340,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f339,f198])).

fof(f339,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f338,f77])).

fof(f338,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f337,f60])).

fof(f337,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f336,f63])).

fof(f336,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f335,f69])).

fof(f335,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f334,f70])).

fof(f334,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ v1_funct_2(sK5,sK3,sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f320,f71])).

fof(f320,plain,(
    ! [X6,X8,X7] :
      ( k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3))
      | ~ m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1)
      | ~ v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5))
      | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(sK5,sK3,sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X6) ) ),
    inference(superposition,[],[f110,f199])).

fof(f110,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f678,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f677])).

fof(f677,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f674,f654])).

fof(f654,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | spl6_1 ),
    inference(backward_demodulation,[],[f467,f650])).

fof(f467,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_1 ),
    inference(backward_demodulation,[],[f317,f463])).

fof(f317,plain,
    ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(superposition,[],[f167,f199])).

fof(f167,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(backward_demodulation,[],[f115,f166])).

fof(f115,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f124,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f72,f121,f117,f113])).

fof(f72,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (28341)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (28338)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (28357)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (28339)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (28344)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (28352)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (28349)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (28345)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (28340)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (28353)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (28362)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (28359)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (28337)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (28348)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (28366)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (28350)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (28354)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (28355)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (28351)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (28361)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (28354)Refutation not found, incomplete strategy% (28354)------------------------------
% 0.20/0.55  % (28354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28354)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28354)Memory used [KB]: 10746
% 0.20/0.55  % (28354)Time elapsed: 0.149 s
% 0.20/0.55  % (28354)------------------------------
% 0.20/0.55  % (28354)------------------------------
% 0.20/0.55  % (28364)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (28347)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (28346)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (28356)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (28360)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (28358)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (28343)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (28342)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (28363)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.57  % (28365)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.73/0.60  % (28359)Refutation not found, incomplete strategy% (28359)------------------------------
% 1.73/0.60  % (28359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (28359)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (28359)Memory used [KB]: 11641
% 1.73/0.60  % (28359)Time elapsed: 0.169 s
% 1.73/0.60  % (28359)------------------------------
% 1.73/0.60  % (28359)------------------------------
% 1.73/0.61  % (28347)Refutation not found, incomplete strategy% (28347)------------------------------
% 1.73/0.61  % (28347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (28347)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (28347)Memory used [KB]: 11385
% 1.73/0.61  % (28347)Time elapsed: 0.199 s
% 1.73/0.61  % (28347)------------------------------
% 1.73/0.61  % (28347)------------------------------
% 2.11/0.64  % (28345)Refutation found. Thanks to Tanya!
% 2.11/0.64  % SZS status Theorem for theBenchmark
% 2.11/0.64  % SZS output start Proof for theBenchmark
% 2.11/0.64  fof(f1257,plain,(
% 2.11/0.64    $false),
% 2.11/0.64    inference(avatar_sat_refutation,[],[f124,f678,f1227,f1241,f1256])).
% 2.11/0.64  fof(f1256,plain,(
% 2.11/0.64    spl6_3 | ~spl6_28),
% 2.11/0.64    inference(avatar_contradiction_clause,[],[f1255])).
% 2.11/0.64  fof(f1255,plain,(
% 2.11/0.64    $false | (spl6_3 | ~spl6_28)),
% 2.11/0.64    inference(subsumption_resolution,[],[f1254,f650])).
% 2.11/0.64  fof(f650,plain,(
% 2.11/0.64    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.11/0.64    inference(resolution,[],[f230,f259])).
% 2.11/0.64  fof(f259,plain,(
% 2.11/0.64    r1_xboole_0(k1_xboole_0,sK2)),
% 2.11/0.64    inference(superposition,[],[f78,f250])).
% 2.11/0.64  fof(f250,plain,(
% 2.11/0.64    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 2.11/0.64    inference(forward_demodulation,[],[f247,f131])).
% 2.11/0.64  fof(f131,plain,(
% 2.11/0.64    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.11/0.64    inference(resolution,[],[f127,f105])).
% 2.11/0.64  fof(f105,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.64    inference(definition_unfolding,[],[f92,f79])).
% 2.11/0.64  fof(f79,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f8])).
% 2.11/0.64  fof(f8,axiom,(
% 2.11/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.11/0.64  fof(f92,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f57])).
% 2.11/0.64  fof(f57,plain,(
% 2.11/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.11/0.64    inference(nnf_transformation,[],[f1])).
% 2.11/0.64  fof(f1,axiom,(
% 2.11/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.11/0.64  fof(f127,plain,(
% 2.11/0.64    r1_xboole_0(sK2,sK3)),
% 2.11/0.64    inference(subsumption_resolution,[],[f126,f61])).
% 2.11/0.64  fof(f61,plain,(
% 2.11/0.64    ~v1_xboole_0(sK2)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f50,plain,(
% 2.11/0.64    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.11/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f49,f48,f47,f46,f45,f44])).
% 2.11/0.64  fof(f44,plain,(
% 2.11/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f45,plain,(
% 2.11/0.64    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f46,plain,(
% 2.11/0.64    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f47,plain,(
% 2.11/0.64    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f48,plain,(
% 2.11/0.64    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f49,plain,(
% 2.11/0.64    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f24,plain,(
% 2.11/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.11/0.64    inference(flattening,[],[f23])).
% 2.11/0.64  fof(f23,plain,(
% 2.11/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.11/0.64    inference(ennf_transformation,[],[f21])).
% 2.11/0.64  fof(f21,negated_conjecture,(
% 2.11/0.64    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.11/0.64    inference(negated_conjecture,[],[f20])).
% 2.11/0.64  fof(f20,conjecture,(
% 2.11/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.11/0.64  fof(f126,plain,(
% 2.11/0.64    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 2.11/0.64    inference(subsumption_resolution,[],[f125,f63])).
% 2.11/0.64  fof(f63,plain,(
% 2.11/0.64    ~v1_xboole_0(sK3)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f125,plain,(
% 2.11/0.64    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 2.11/0.64    inference(resolution,[],[f65,f86])).
% 2.11/0.64  fof(f86,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f54])).
% 2.11/0.64  fof(f54,plain,(
% 2.11/0.64    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.11/0.64    inference(nnf_transformation,[],[f34])).
% 2.11/0.64  fof(f34,plain,(
% 2.11/0.64    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.11/0.64    inference(flattening,[],[f33])).
% 2.11/0.64  fof(f33,plain,(
% 2.11/0.64    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.11/0.64    inference(ennf_transformation,[],[f12])).
% 2.11/0.64  fof(f12,axiom,(
% 2.11/0.64    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.11/0.64  fof(f65,plain,(
% 2.11/0.64    r1_subset_1(sK2,sK3)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f247,plain,(
% 2.11/0.64    k1_setfam_1(k2_tarski(sK2,sK3)) = k4_xboole_0(sK2,sK2)),
% 2.11/0.64    inference(superposition,[],[f103,f132])).
% 2.11/0.64  fof(f132,plain,(
% 2.11/0.64    sK2 = k4_xboole_0(sK2,sK3)),
% 2.11/0.64    inference(resolution,[],[f127,f90])).
% 2.11/0.64  fof(f90,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.11/0.64    inference(cnf_transformation,[],[f56])).
% 2.11/0.64  fof(f56,plain,(
% 2.11/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.11/0.64    inference(nnf_transformation,[],[f5])).
% 2.11/0.64  fof(f5,axiom,(
% 2.11/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.11/0.64  fof(f103,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.64    inference(definition_unfolding,[],[f80,f79])).
% 2.11/0.64  fof(f80,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f3])).
% 2.11/0.64  fof(f3,axiom,(
% 2.11/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.11/0.64  fof(f78,plain,(
% 2.11/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f4])).
% 2.11/0.64  fof(f4,axiom,(
% 2.11/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.11/0.64  fof(f230,plain,(
% 2.11/0.64    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1)) )),
% 2.11/0.64    inference(subsumption_resolution,[],[f228,f151])).
% 2.11/0.64  fof(f151,plain,(
% 2.11/0.64    v1_relat_1(sK4)),
% 2.11/0.64    inference(resolution,[],[f68,f97])).
% 2.11/0.64  fof(f97,plain,(
% 2.11/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f38])).
% 2.11/0.64  fof(f38,plain,(
% 2.11/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.64    inference(ennf_transformation,[],[f13])).
% 2.11/0.64  fof(f13,axiom,(
% 2.11/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.11/0.64  fof(f68,plain,(
% 2.11/0.64    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f228,plain,(
% 2.11/0.64    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1) | ~v1_relat_1(sK4)) )),
% 2.11/0.64    inference(superposition,[],[f76,f216])).
% 2.11/0.64  fof(f216,plain,(
% 2.11/0.64    sK2 = k1_relat_1(sK4)),
% 2.11/0.64    inference(subsumption_resolution,[],[f215,f151])).
% 2.11/0.64  fof(f215,plain,(
% 2.11/0.64    sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 2.11/0.64    inference(subsumption_resolution,[],[f214,f150])).
% 2.11/0.64  fof(f150,plain,(
% 2.11/0.64    v4_relat_1(sK4,sK2)),
% 2.11/0.64    inference(resolution,[],[f68,f98])).
% 2.11/0.64  fof(f98,plain,(
% 2.11/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f39])).
% 2.11/0.64  fof(f39,plain,(
% 2.11/0.64    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.64    inference(ennf_transformation,[],[f22])).
% 2.11/0.64  fof(f22,plain,(
% 2.11/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.11/0.64    inference(pure_predicate_removal,[],[f14])).
% 2.11/0.64  fof(f14,axiom,(
% 2.11/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.11/0.64  fof(f214,plain,(
% 2.11/0.64    sK2 = k1_relat_1(sK4) | ~v4_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 2.11/0.64    inference(resolution,[],[f170,f88])).
% 2.11/0.64  fof(f88,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f55])).
% 2.11/0.64  fof(f55,plain,(
% 2.11/0.64    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.11/0.64    inference(nnf_transformation,[],[f36])).
% 2.11/0.64  fof(f36,plain,(
% 2.11/0.64    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.11/0.64    inference(flattening,[],[f35])).
% 2.11/0.64  fof(f35,plain,(
% 2.11/0.64    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.11/0.64    inference(ennf_transformation,[],[f16])).
% 2.11/0.64  fof(f16,axiom,(
% 2.11/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 2.11/0.64  fof(f170,plain,(
% 2.11/0.64    v1_partfun1(sK4,sK2)),
% 2.11/0.64    inference(subsumption_resolution,[],[f169,f60])).
% 2.11/0.64  fof(f60,plain,(
% 2.11/0.64    ~v1_xboole_0(sK1)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f169,plain,(
% 2.11/0.64    v1_partfun1(sK4,sK2) | v1_xboole_0(sK1)),
% 2.11/0.64    inference(subsumption_resolution,[],[f168,f66])).
% 2.11/0.64  fof(f66,plain,(
% 2.11/0.64    v1_funct_1(sK4)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f168,plain,(
% 2.11/0.64    ~v1_funct_1(sK4) | v1_partfun1(sK4,sK2) | v1_xboole_0(sK1)),
% 2.11/0.64    inference(subsumption_resolution,[],[f152,f67])).
% 2.11/0.64  fof(f67,plain,(
% 2.11/0.64    v1_funct_2(sK4,sK2,sK1)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f152,plain,(
% 2.11/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_partfun1(sK4,sK2) | v1_xboole_0(sK1)),
% 2.11/0.64    inference(resolution,[],[f68,f82])).
% 2.11/0.64  fof(f82,plain,(
% 2.11/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f30])).
% 2.11/0.64  fof(f30,plain,(
% 2.11/0.64    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.11/0.64    inference(flattening,[],[f29])).
% 2.11/0.64  fof(f29,plain,(
% 2.11/0.64    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.11/0.64    inference(ennf_transformation,[],[f15])).
% 2.11/0.64  fof(f15,axiom,(
% 2.11/0.64    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.11/0.64  fof(f76,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f27])).
% 2.11/0.64  fof(f27,plain,(
% 2.11/0.64    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.11/0.64    inference(ennf_transformation,[],[f11])).
% 2.11/0.64  fof(f11,axiom,(
% 2.11/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 2.11/0.64  fof(f1254,plain,(
% 2.11/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (spl6_3 | ~spl6_28)),
% 2.11/0.64    inference(forward_demodulation,[],[f1253,f674])).
% 2.11/0.64  fof(f674,plain,(
% 2.11/0.64    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.11/0.64    inference(resolution,[],[f236,f369])).
% 2.11/0.64  fof(f369,plain,(
% 2.11/0.64    r1_xboole_0(k1_xboole_0,sK3)),
% 2.11/0.64    inference(superposition,[],[f78,f256])).
% 2.11/0.64  fof(f256,plain,(
% 2.11/0.64    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 2.11/0.64    inference(forward_demodulation,[],[f253,f140])).
% 2.11/0.64  fof(f140,plain,(
% 2.11/0.64    k1_xboole_0 = k1_setfam_1(k2_tarski(sK3,sK2))),
% 2.11/0.64    inference(resolution,[],[f134,f105])).
% 2.11/0.64  fof(f134,plain,(
% 2.11/0.64    r1_xboole_0(sK3,sK2)),
% 2.11/0.64    inference(resolution,[],[f127,f85])).
% 2.11/0.64  fof(f85,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f32])).
% 2.11/0.64  fof(f32,plain,(
% 2.11/0.64    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.11/0.64    inference(ennf_transformation,[],[f2])).
% 2.11/0.64  fof(f2,axiom,(
% 2.11/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.11/0.64  fof(f253,plain,(
% 2.11/0.64    k1_setfam_1(k2_tarski(sK3,sK2)) = k4_xboole_0(sK3,sK3)),
% 2.11/0.64    inference(superposition,[],[f103,f141])).
% 2.11/0.64  fof(f141,plain,(
% 2.11/0.64    sK3 = k4_xboole_0(sK3,sK2)),
% 2.11/0.64    inference(resolution,[],[f134,f90])).
% 2.11/0.64  fof(f236,plain,(
% 2.11/0.64    ( ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1)) )),
% 2.11/0.64    inference(subsumption_resolution,[],[f234,f184])).
% 2.11/0.64  fof(f184,plain,(
% 2.11/0.64    v1_relat_1(sK5)),
% 2.11/0.64    inference(resolution,[],[f71,f97])).
% 2.11/0.64  fof(f71,plain,(
% 2.11/0.64    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f234,plain,(
% 2.11/0.64    ( ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1) | ~v1_relat_1(sK5)) )),
% 2.11/0.64    inference(superposition,[],[f76,f222])).
% 2.11/0.64  fof(f222,plain,(
% 2.11/0.64    sK3 = k1_relat_1(sK5)),
% 2.11/0.64    inference(subsumption_resolution,[],[f221,f184])).
% 2.11/0.64  fof(f221,plain,(
% 2.11/0.64    sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 2.11/0.64    inference(subsumption_resolution,[],[f220,f183])).
% 2.11/0.64  fof(f183,plain,(
% 2.11/0.64    v4_relat_1(sK5,sK3)),
% 2.11/0.64    inference(resolution,[],[f71,f98])).
% 2.11/0.64  fof(f220,plain,(
% 2.11/0.64    sK3 = k1_relat_1(sK5) | ~v4_relat_1(sK5,sK3) | ~v1_relat_1(sK5)),
% 2.11/0.64    inference(resolution,[],[f202,f88])).
% 2.11/0.64  fof(f202,plain,(
% 2.11/0.64    v1_partfun1(sK5,sK3)),
% 2.11/0.64    inference(subsumption_resolution,[],[f201,f60])).
% 2.11/0.64  fof(f201,plain,(
% 2.11/0.64    v1_partfun1(sK5,sK3) | v1_xboole_0(sK1)),
% 2.11/0.64    inference(subsumption_resolution,[],[f200,f69])).
% 2.11/0.64  fof(f69,plain,(
% 2.11/0.64    v1_funct_1(sK5)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f200,plain,(
% 2.11/0.64    ~v1_funct_1(sK5) | v1_partfun1(sK5,sK3) | v1_xboole_0(sK1)),
% 2.11/0.64    inference(subsumption_resolution,[],[f185,f70])).
% 2.11/0.64  fof(f70,plain,(
% 2.11/0.64    v1_funct_2(sK5,sK3,sK1)),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.64  fof(f185,plain,(
% 2.11/0.64    ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | v1_partfun1(sK5,sK3) | v1_xboole_0(sK1)),
% 2.11/0.64    inference(resolution,[],[f71,f82])).
% 2.11/0.64  fof(f1253,plain,(
% 2.11/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (spl6_3 | ~spl6_28)),
% 2.11/0.64    inference(subsumption_resolution,[],[f1252,f62])).
% 2.11/0.64  fof(f62,plain,(
% 2.11/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(cnf_transformation,[],[f50])).
% 2.11/0.65  fof(f1252,plain,(
% 2.11/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (spl6_3 | ~spl6_28)),
% 2.11/0.65    inference(subsumption_resolution,[],[f1251,f64])).
% 2.11/0.65  fof(f64,plain,(
% 2.11/0.65    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.11/0.65    inference(cnf_transformation,[],[f50])).
% 2.11/0.65  fof(f1251,plain,(
% 2.11/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (spl6_3 | ~spl6_28)),
% 2.11/0.65    inference(subsumption_resolution,[],[f1250,f123])).
% 2.11/0.65  fof(f123,plain,(
% 2.11/0.65    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_3),
% 2.11/0.65    inference(avatar_component_clause,[],[f121])).
% 2.11/0.65  fof(f121,plain,(
% 2.11/0.65    spl6_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.11/0.65  fof(f1250,plain,(
% 2.11/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1248,f1225])).
% 2.11/0.65  fof(f1225,plain,(
% 2.11/0.65    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_28),
% 2.11/0.65    inference(avatar_component_clause,[],[f1224])).
% 2.11/0.65  fof(f1224,plain,(
% 2.11/0.65    spl6_28 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.11/0.65  fof(f1248,plain,(
% 2.11/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.11/0.65    inference(superposition,[],[f847,f463])).
% 2.11/0.65  fof(f463,plain,(
% 2.11/0.65    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3)),
% 2.11/0.65    inference(superposition,[],[f131,f136])).
% 2.11/0.65  fof(f136,plain,(
% 2.11/0.65    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3))) )),
% 2.11/0.65    inference(resolution,[],[f64,f106])).
% 2.11/0.65  fof(f106,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.11/0.65    inference(definition_unfolding,[],[f96,f79])).
% 2.11/0.65  fof(f96,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f37])).
% 2.11/0.65  fof(f37,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.11/0.65    inference(ennf_transformation,[],[f6])).
% 2.11/0.65  fof(f6,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.11/0.65  fof(f847,plain,(
% 2.11/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f846,f61])).
% 2.11/0.65  fof(f846,plain,(
% 2.11/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f845,f66])).
% 2.11/0.65  fof(f845,plain,(
% 2.11/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f844,f67])).
% 2.11/0.65  fof(f844,plain,(
% 2.11/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f832,f68])).
% 2.11/0.65  fof(f832,plain,(
% 2.11/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.11/0.65    inference(superposition,[],[f349,f166])).
% 2.11/0.65  fof(f166,plain,(
% 2.11/0.65    ( ! [X6] : (k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f149,f66])).
% 2.11/0.65  fof(f149,plain,(
% 2.11/0.65    ( ! [X6] : (k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6) | ~v1_funct_1(sK4)) )),
% 2.11/0.65    inference(resolution,[],[f68,f99])).
% 2.11/0.65  fof(f99,plain,(
% 2.11/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f41])).
% 2.11/0.65  fof(f41,plain,(
% 2.11/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.11/0.65    inference(flattening,[],[f40])).
% 2.11/0.65  fof(f40,plain,(
% 2.11/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.11/0.65    inference(ennf_transformation,[],[f17])).
% 2.11/0.65  fof(f17,axiom,(
% 2.11/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.11/0.65  fof(f349,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f348,f193])).
% 2.11/0.65  fof(f193,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f192,f77])).
% 2.11/0.65  fof(f77,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f28])).
% 2.11/0.65  fof(f28,plain,(
% 2.11/0.65    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.11/0.65    inference(ennf_transformation,[],[f7])).
% 2.11/0.65  fof(f7,axiom,(
% 2.11/0.65    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.11/0.65  fof(f192,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f191,f60])).
% 2.11/0.65  fof(f191,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f190,f63])).
% 2.11/0.65  fof(f190,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_xboole_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f189,f69])).
% 2.11/0.65  fof(f189,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_xboole_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f180,f70])).
% 2.11/0.65  fof(f180,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),k4_subset_1(X0,X1,sK3),sK1) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_xboole_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(resolution,[],[f71,f101])).
% 2.11/0.65  fof(f101,plain,(
% 2.11/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f43])).
% 2.11/0.65  fof(f43,plain,(
% 2.11/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.11/0.65    inference(flattening,[],[f42])).
% 2.11/0.65  fof(f42,plain,(
% 2.11/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.11/0.65    inference(ennf_transformation,[],[f19])).
% 2.11/0.65  fof(f19,axiom,(
% 2.11/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.11/0.65  fof(f348,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f347,f198])).
% 2.11/0.65  fof(f198,plain,(
% 2.11/0.65    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f197,f77])).
% 2.11/0.65  fof(f197,plain,(
% 2.11/0.65    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f196,f60])).
% 2.11/0.65  fof(f196,plain,(
% 2.11/0.65    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f195,f63])).
% 2.11/0.65  fof(f195,plain,(
% 2.11/0.65    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f194,f69])).
% 2.11/0.65  fof(f194,plain,(
% 2.11/0.65    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f181,f70])).
% 2.11/0.65  fof(f181,plain,(
% 2.11/0.65    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 2.11/0.65    inference(resolution,[],[f71,f102])).
% 2.11/0.65  fof(f102,plain,(
% 2.11/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f43])).
% 2.11/0.65  fof(f347,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f346,f77])).
% 2.11/0.65  fof(f346,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10) | v1_xboole_0(X9)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f345,f60])).
% 2.11/0.65  fof(f345,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10) | v1_xboole_0(sK1) | v1_xboole_0(X9)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f344,f63])).
% 2.11/0.65  fof(f344,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | v1_xboole_0(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10) | v1_xboole_0(sK1) | v1_xboole_0(X9)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f343,f69])).
% 2.11/0.65  fof(f343,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~v1_funct_1(sK5) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | v1_xboole_0(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10) | v1_xboole_0(sK1) | v1_xboole_0(X9)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f342,f70])).
% 2.11/0.65  fof(f342,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | v1_xboole_0(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10) | v1_xboole_0(sK1) | v1_xboole_0(X9)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f321,f71])).
% 2.11/0.65  fof(f321,plain,(
% 2.11/0.65    ( ! [X10,X11,X9] : (k7_relat_1(sK5,k9_subset_1(X9,X10,sK3)) != k2_partfun1(X10,sK1,X11,k9_subset_1(X9,X10,sK3)) | ~m1_subset_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X9,X10,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),k4_subset_1(X9,X10,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X9,sK1,X10,sK3,X11,sK5)) | sK5 = k2_partfun1(k4_subset_1(X9,X10,sK3),sK1,k1_tmap_1(X9,sK1,X10,sK3,X11,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | ~v1_funct_2(X11,X10,sK1) | ~v1_funct_1(X11) | ~m1_subset_1(sK3,k1_zfmisc_1(X9)) | v1_xboole_0(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | v1_xboole_0(X10) | v1_xboole_0(sK1) | v1_xboole_0(X9)) )),
% 2.11/0.65    inference(superposition,[],[f109,f199])).
% 2.11/0.65  fof(f199,plain,(
% 2.11/0.65    ( ! [X6] : (k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f182,f69])).
% 2.11/0.65  fof(f182,plain,(
% 2.11/0.65    ( ! [X6] : (k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6) | ~v1_funct_1(sK5)) )),
% 2.11/0.65    inference(resolution,[],[f71,f99])).
% 2.11/0.65  fof(f109,plain,(
% 2.11/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(equality_resolution,[],[f74])).
% 2.11/0.65  fof(f74,plain,(
% 2.11/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f52])).
% 2.11/0.65  fof(f52,plain,(
% 2.11/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.11/0.65    inference(flattening,[],[f51])).
% 2.11/0.65  fof(f51,plain,(
% 2.11/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.11/0.65    inference(nnf_transformation,[],[f26])).
% 2.11/0.65  fof(f26,plain,(
% 2.11/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.11/0.65    inference(flattening,[],[f25])).
% 2.11/0.65  fof(f25,plain,(
% 2.11/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.11/0.65    inference(ennf_transformation,[],[f18])).
% 2.11/0.65  fof(f18,axiom,(
% 2.11/0.65    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.11/0.65  fof(f1241,plain,(
% 2.11/0.65    spl6_28),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f1240])).
% 2.11/0.65  fof(f1240,plain,(
% 2.11/0.65    $false | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1239,f59])).
% 2.11/0.65  fof(f59,plain,(
% 2.11/0.65    ~v1_xboole_0(sK0)),
% 2.11/0.65    inference(cnf_transformation,[],[f50])).
% 2.11/0.65  fof(f1239,plain,(
% 2.11/0.65    v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1238,f60])).
% 2.11/0.65  fof(f1238,plain,(
% 2.11/0.65    v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1237,f61])).
% 2.11/0.65  fof(f1237,plain,(
% 2.11/0.65    v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1236,f62])).
% 2.11/0.65  fof(f1236,plain,(
% 2.11/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1235,f63])).
% 2.11/0.65  fof(f1235,plain,(
% 2.11/0.65    v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1234,f64])).
% 2.11/0.65  fof(f1234,plain,(
% 2.11/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1233,f66])).
% 2.11/0.65  fof(f1233,plain,(
% 2.11/0.65    ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1232,f67])).
% 2.11/0.65  fof(f1232,plain,(
% 2.11/0.65    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1231,f68])).
% 2.11/0.65  fof(f1231,plain,(
% 2.11/0.65    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1230,f69])).
% 2.11/0.65  fof(f1230,plain,(
% 2.11/0.65    ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.11/0.65    inference(subsumption_resolution,[],[f1229,f70])).
% 2.19/0.65  fof(f1229,plain,(
% 2.19/0.65    ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.19/0.65    inference(subsumption_resolution,[],[f1228,f71])).
% 2.19/0.65  fof(f1228,plain,(
% 2.19/0.65    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_28),
% 2.19/0.65    inference(resolution,[],[f1226,f100])).
% 2.19/0.65  fof(f100,plain,(
% 2.19/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f43])).
% 2.19/0.65  fof(f1226,plain,(
% 2.19/0.65    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | spl6_28),
% 2.19/0.65    inference(avatar_component_clause,[],[f1224])).
% 2.19/0.65  fof(f1227,plain,(
% 2.19/0.65    spl6_2 | ~spl6_28),
% 2.19/0.65    inference(avatar_split_clause,[],[f1222,f1224,f117])).
% 2.19/0.65  fof(f117,plain,(
% 2.19/0.65    spl6_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.19/0.65  fof(f1222,plain,(
% 2.19/0.65    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.19/0.65    inference(subsumption_resolution,[],[f1221,f650])).
% 2.19/0.65  fof(f1221,plain,(
% 2.19/0.65    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.19/0.65    inference(forward_demodulation,[],[f1220,f674])).
% 2.19/0.65  fof(f1220,plain,(
% 2.19/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.19/0.65    inference(subsumption_resolution,[],[f1219,f62])).
% 2.19/0.65  fof(f1219,plain,(
% 2.19/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.19/0.65    inference(subsumption_resolution,[],[f1198,f64])).
% 2.19/0.65  fof(f1198,plain,(
% 2.19/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.19/0.65    inference(superposition,[],[f823,f463])).
% 2.19/0.65  fof(f823,plain,(
% 2.19/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f822,f61])).
% 2.19/0.65  fof(f822,plain,(
% 2.19/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f821,f66])).
% 2.19/0.65  fof(f821,plain,(
% 2.19/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f820,f67])).
% 2.19/0.65  fof(f820,plain,(
% 2.19/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f808,f68])).
% 2.19/0.65  fof(f808,plain,(
% 2.19/0.65    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2)) )),
% 2.19/0.65    inference(superposition,[],[f341,f166])).
% 2.19/0.65  fof(f341,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f340,f193])).
% 2.19/0.65  fof(f340,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f339,f198])).
% 2.19/0.65  fof(f339,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f338,f77])).
% 2.19/0.65  fof(f338,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7) | v1_xboole_0(X6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f337,f60])).
% 2.19/0.65  fof(f337,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7) | v1_xboole_0(sK1) | v1_xboole_0(X6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f336,f63])).
% 2.19/0.65  fof(f336,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | v1_xboole_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7) | v1_xboole_0(sK1) | v1_xboole_0(X6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f335,f69])).
% 2.19/0.65  fof(f335,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | v1_xboole_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7) | v1_xboole_0(sK1) | v1_xboole_0(X6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f334,f70])).
% 2.19/0.65  fof(f334,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | v1_xboole_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7) | v1_xboole_0(sK1) | v1_xboole_0(X6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f320,f71])).
% 2.19/0.65  fof(f320,plain,(
% 2.19/0.65    ( ! [X6,X8,X7] : (k7_relat_1(sK5,k9_subset_1(X6,X7,sK3)) != k2_partfun1(X7,sK1,X8,k9_subset_1(X6,X7,sK3)) | ~m1_subset_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,X7,sK3),sK1))) | ~v1_funct_2(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),k4_subset_1(X6,X7,sK3),sK1) | ~v1_funct_1(k1_tmap_1(X6,sK1,X7,sK3,X8,sK5)) | k2_partfun1(k4_subset_1(X6,X7,sK3),sK1,k1_tmap_1(X6,sK1,X7,sK3,X8,sK5),X7) = X8 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) | ~v1_funct_2(X8,X7,sK1) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | v1_xboole_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | v1_xboole_0(X7) | v1_xboole_0(sK1) | v1_xboole_0(X6)) )),
% 2.19/0.65    inference(superposition,[],[f110,f199])).
% 2.19/0.65  fof(f110,plain,(
% 2.19/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.19/0.65    inference(equality_resolution,[],[f73])).
% 2.19/0.65  fof(f73,plain,(
% 2.19/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f52])).
% 2.19/0.65  fof(f678,plain,(
% 2.19/0.65    spl6_1),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f677])).
% 2.19/0.65  fof(f677,plain,(
% 2.19/0.65    $false | spl6_1),
% 2.19/0.65    inference(subsumption_resolution,[],[f674,f654])).
% 2.19/0.65  fof(f654,plain,(
% 2.19/0.65    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | spl6_1),
% 2.19/0.65    inference(backward_demodulation,[],[f467,f650])).
% 2.19/0.65  fof(f467,plain,(
% 2.19/0.65    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl6_1),
% 2.19/0.65    inference(backward_demodulation,[],[f317,f463])).
% 2.19/0.65  fof(f317,plain,(
% 2.19/0.65    k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 2.19/0.65    inference(superposition,[],[f167,f199])).
% 2.19/0.65  fof(f167,plain,(
% 2.19/0.65    k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 2.19/0.65    inference(backward_demodulation,[],[f115,f166])).
% 2.19/0.65  fof(f115,plain,(
% 2.19/0.65    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 2.19/0.65    inference(avatar_component_clause,[],[f113])).
% 2.19/0.65  fof(f113,plain,(
% 2.19/0.65    spl6_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.19/0.65  fof(f124,plain,(
% 2.19/0.65    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 2.19/0.65    inference(avatar_split_clause,[],[f72,f121,f117,f113])).
% 2.19/0.65  fof(f72,plain,(
% 2.19/0.65    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  % SZS output end Proof for theBenchmark
% 2.19/0.65  % (28345)------------------------------
% 2.19/0.65  % (28345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (28345)Termination reason: Refutation
% 2.19/0.65  
% 2.19/0.65  % (28345)Memory used [KB]: 12025
% 2.19/0.65  % (28345)Time elapsed: 0.233 s
% 2.19/0.65  % (28345)------------------------------
% 2.19/0.65  % (28345)------------------------------
% 2.19/0.65  % (28336)Success in time 0.292 s
%------------------------------------------------------------------------------
